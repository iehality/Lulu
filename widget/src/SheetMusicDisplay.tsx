import React, { useEffect, useRef } from 'react';
import { OpenSheetMusicDisplay } from 'opensheetmusicdisplay';

type SheetMusicDisplayProps = {
  musicXML: string;
};

const SheetMusicDisplay: React.FC<SheetMusicDisplayProps> = ({ musicXML }) => {
  const containerRef = useRef<HTMLDivElement | null>(null);
  const osmdRef = useRef<OpenSheetMusicDisplay | null>(null);

  useEffect(() => {
    if (!containerRef.current) return;

    osmdRef.current = new OpenSheetMusicDisplay(containerRef.current, {
      autoResize: true,
    });

    if (musicXML) {
      loadMusic(musicXML);
    }

    return () => {
      osmdRef.current = null;
    };
  }, [musicXML]);

  const loadMusic = async (xml: string) => {
    try {
      if (osmdRef.current) {
        await osmdRef.current.load(xml);

        osmdRef.current.setOptions({
          drawTitle: false,
          drawPartNames: false
        });

        osmdRef.current.render();
      }
    } catch (error) {
      console.error('Error loading or rendering music XML:', error);
    }
  };

  return <div ref={containerRef} style={{ width: '100%', height: 'auto' }} />;
};

export default SheetMusicDisplay;

